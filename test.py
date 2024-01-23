import numpy as np
import matplotlib.pyplot as plt

def calculate_general_matrix(layer_indices, layer_thicknesses, wavelength, angle_of_incidence):
    # Initialize the general matrix
    general_matrix = np.eye(2, dtype=complex)

    # Iterate over the layers
    for i in range(len(layer_indices)):
        # Calculate the wavevector in each layer
        k = 2 * np.pi * layer_indices[i] * layer_thicknesses[i] * np.cos(angle_of_incidence) / wavelength

        # Calculate the layer matrix without absorption
        layer_matrix = np.array([[np.cos(k), 1j * np.sin(k)],
                                 [1j * np.sin(k), np.cos(k)]])

        # Multiply the general matrix with the layer matrix
        general_matrix = np.matmul(general_matrix, layer_matrix)

    return general_matrix

# Example usage
layer_indices = [1.5, 1.8, 1.2]  # Refractive indices of the layers
layer_thicknesses = [100, 200, 150]  # Thicknesses of the layers in nm
wavelength = 500  # Wavelength in nm
angle_of_incidence = np.deg2rad(45)  # Angle of incidence in radians

general_matrix = calculate_general_matrix(layer_indices, layer_thicknesses, wavelength, angle_of_incidence)

# Plot the real and imaginary parts of the matrix
plt.figure()
plt.subplot(1, 2, 1)
plt.imshow(np.real(general_matrix), cmap='hot', interpolation='nearest')
plt.title('Real Part')
plt.colorbar()

plt.subplot(1, 2, 2)
plt.imshow(np.imag(general_matrix), cmap='hot', interpolation='nearest')
plt.title('Imaginary Part')
plt.colorbar()

plt.show()
